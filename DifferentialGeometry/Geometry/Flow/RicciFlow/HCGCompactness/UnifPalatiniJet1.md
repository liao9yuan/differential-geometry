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

RETIRED 2026-08-02 (verification pass, ledger No. 97): the `Λ < 2`
migration this section used to demand is DONE — `unifCurvSup` and
`unifRmJetOne` (`UnifCurvatureJetOne.lean:876`) take only `1 ≤ Λ` — and
`unifKsupLeOne` EXISTS sorry-free at `UnifDeTurckRHSOne.lean:1538` with
`∃ Kstar` quantified before `∀ g₀`.  See `ShortTime/PALATINI_WALL_PLAN.md`
for the grep-verified closure inventory.  The only dormant residue in this
area is the all-order abstract `hcurv` of `UnifBochnerGap.lean:304`
(no live consumer).

## Project accounting

`ricci_flow_unif_existence` itself remains 0%. The field-level Palatini
wall is CLOSED for arbitrary comparability, including its three consumers
(`a = 1` envelope, class-uniform `Ksup` at `j = 1`, and `unifFc` — the
latter dissolved by ledger No. 85).
