# DeTurckRemainderLowBaseAction

## Role

This is the intrinsic fixed-order smooth-core module for the low-regularity
Ricci--DeTurck remainder.  It refolds the dangerous Ricci zero-head at the
self-action level before any Sobolev estimate is taken.

## Verified state

Focused verification is GREEN and warning-free.  The file is below the
3000-line limit and contains no `sorry`, `admit`, axiom declaration, `whnf`,
or trace command.

The public surface is now limited to:

- `lowJetSq`;
- `LowBaseActionData` and its `a1`/`a2` actions;
- the exact zero-based split `remainder_low_split`;
- the fixed three-dimensional coefficient-envelope estimates `a1_h3_h2` and
  `a1_h2_h1`.

The exact algebra is complete.  In particular, the connection-difference
Ricci head is split into a true lower coefficient and a transposed
second-order self-action, then integrated in the path parameter.  No
arbitrary-passenger operator identity is assumed.

## Remaining frontier

The final state-dependent low-base producer is not yet stated or proved
(0%).  The generic A1 scale estimates are proved, but they still require an
`H2` envelope for `C0` and `C1`.  The complete `C2` fibre-small estimate also
remains to be attached to the exact split.

The precise missing producer is a fixed `q = 0,1,2` radius-free bound for the
`rhsSelfLow` path family, followed by the corresponding path-integral
transfer.  The needed cancellation-preserving Lie fields and their exact
decomposition currently exist only as private declarations in
`DeTurckRemainderTameLipschitz.lean`; the public radius-free wrappers still
require a supercritical order `a` and `ha_super`, so they are not valid inputs
to this module.

The smallest next lemma is a private `rhsSelfLow` H2-jet envelope whose
constants and polynomial degree are chosen before `T` and whose right-hand
side uses only `1 + lowJetSq g 3 T`.  It must be proved from fixed-order
producers, not from an all-order ball theorem.

The live API audit confirms that this is a genuine lower-layer gap:

- the cancellation-preserving `lc0CdVField`, `lc0VBField`, `lc0AMixField`,
  `lc0RiemField`, and their two exact decomposition lemmas are private inside
  the 46k-line tame-Lipschitz reference module;
- extracting those declarations also requires their private fibre/model
  realization chain, so it does not fit the remaining line budget as a local
  copy, and importing that module would invert the intended dependency;
- the chart first-order remainder proves the correct local symbol statement,
  but no global intrinsic value/first-jet realization producer is available
  to turn it into the required smooth coefficient fields.

Thus the next canonical implementation step is to expose a small fixed-order
Lie cancellation producer at the coefficient layer, with no `a`, high-order
ball, or radius parameter.  The present Action module should then consume that
producer to prove the state-polynomial envelope and complete `C2` smallness.

The historical Pair and Zero modules have now been retired to import-only
compatibility shims.  They have no declaration consumers and both pass focused
verification against the refreshed Action artifact, so the removed
`extraA2Act` and `rhsRefold2Int` facades no longer create a stale downstream
risk.

## Progress accounting

- exact smooth-core zero-based action identity: 100%;
- generic H3-to-H2 and H2-to-H1 estimates for the same A1 formula: 100%;
- state-polynomial coefficient envelope and complete A2 smallness: 0% as a
  theorem, with substantial exact/refold machinery already present;
- final `LowBaseActionSplit`: unstated/unproved, 0%;
- `ricci_flow_unif_existence`: unstated/unproved, 0%; its dedicated machinery
  is approximately 90--92%.
