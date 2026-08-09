# EdgeRiemCancel

## Current source state

`EdgeRiemCancel.lean` contains a placeholder-free exact Riemann-cancellation
producer.  Its post-merge source is focused-green.  The original public
statements are preserved and one stronger producer is exported.

The file exports:

- `edgeRiem_cancel`, the algebraic fact that a complete Riemann refold cancels
  the Riemann half inserted in `edgeRicciHalf`;
- `edgeLie_inner` and `edgeLie_green`, the exact formal-partner and Green
  identities for the DeTurck Lie family alone; and
- `exists_edgeLieRef`, which rebuilds the canonical public Palatini and
  DeTurck refold data, cancels the Riemann block, and returns a normal form
  containing only the genuine Ricci connection-difference coefficient, a
  uniformly bounded order-zero family, the already visible lower arms, and
  the Lie pair family.
- `exists_edgeLieJoint`, which retains the same exact normal form together
  with the joint-smooth order-zero family needed before path integration;
  `exists_edgeLieRef` is now its compatibility projection.

`edgeRiem_cancel` is already polymorphic in its acted tensor `W`, but it is a
consumer of a supplied, correctly oriented refold identity.  It does not
produce that identity.  In particular, the diagonal Palatini producer cannot
be frozen by replacing only the acted state: the true off-diagonal refold has
the independent passenger in the top coefficient and keeps `nabla^2` on the
path state.  A conditional `edgeRiem_cancel_bi` alias would therefore add no
content, while a reversed `C2(P) (nabla^2 U)` producer would be false.

The producer adds no hypothesis.  Its internal finite jet radius is used only
to instantiate the already proved exact refold identities for the fixed smooth
edge tensor; no such radius appears in the theorem statement or downstream
estimate.

The first post-merge artifact refresh exposed only API drift: the old real
inner-product notation no longer parsed in these statements, the
`MetricRealization` names were no longer in scope, and the duplicated raw
normalization relied on fragile half-coefficient reduction.  The source now
uses `Inner.inner Real`, opens the canonical namespace, and reuses
`edgeRiem_cancel` for that normalization.  Focused verification then passed.

## Mathematical consequence

The earlier combined top coefficient spent a separate smallness budget on a
Riemann second-order partner.  That was unnecessary: the Riemann order-zero
and second-order pieces are the two sides of one exact Palatini identity.
After cancellation, only the Lie formal partner needs a boundary energy
estimate.

This does not by itself prove `ricci_flow_forward_unique`.  The unchanged
endpoint remains **0%** until all surviving Ricci/DeTurck arms are absorbed,
the closed-edge energy theorem is assembled, and geometric Ricci-flow gauge
uniqueness is completed.

## Verification

- Source placeholders (`sorry`, `admit`, axiom): none.
- Focused Lean check: passed.
- The stronger `exists_edgeLieJoint` producer passed focused verification at
  the shared resource cap.
- Exact artifact refresh: the pre-repair attempt failed on the API drift above;
  the repaired source then passed its coordinated exact refresh.
- `extends_of_rmBounded`: unchanged.
