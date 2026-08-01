# UnifPalatiniJet1

## Role

This HCG sibling consumes the canonical differentiated Palatini identity and
the already banked class-uniform bounds for `A`, `∇A`, and `∇²A`.

## Current state

`unifPalatini1` is proved.  It gives a class-uniform fixed-order quadrilinear
bound for the canonical pointwise differentiated Palatini vector using metric
jets only through order three.  Both focused verification and the exact
targeted module refresh passed, and direct axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.

The proof uses the canonical `covDerivPal_eq` split together with the explicit
ungated bounds for `A`, `∇A`, and `∇²A`.  Its public signature now assumes only
`1 ≤ Λ`; the former `Λ < 2` hypothesis was an artifact of the old perturbative
`A₀/A₁` producers.  The older HCG-local
`covDerivConnDiff2` is definitionally identical to the canonical curvature
layer definition; a private equality bridge keeps the public API canonical.

## Remaining frontier

The Palatini producer is now arbitrary-`Λ`, but its direct consumers in
`UnifCurvatureJetOne.lean` still carry the staged `Λ < 2` argument.  The next
brick is to migrate `curvConn_le`, `unifRmOpOne`, and `unifRmSecOne` to
`unifCurvSup` plus this new signature, then propagate that removal into the
static `j = 1` Ricci--DeTurck bound.

## Project accounting

`ricci_flow_unif_existence` itself remains 0%. This closes the field-level
Palatini wall for arbitrary comparability inside the dedicated machinery.
The final `unifKsupLeOne` theorem is still unstated (0%); its dedicated
finite-order geometric producers are now substantially closer, while the
consumer migration and uniform witness assembly remain.
