# HomogeneousMaster

## Goal

`hom_master_nonsmooth` is the generic Euclidean producer converting a local
De Giorgi homogeneous weak solution and a locally matching smooth coefficient
into the exact nonsmooth Nirenberg master inequality.

The public theorem and its dedicated per-step identity are now source-written
and focused-verified without warnings.

## Native route

1. Consume the explicit local standard-test identity from
   `HomogeneousWeakSolution.lean`.
2. Replace `A.a` by `rho * B.a` only on
   `cthickening R0 (tsupport eta)` and cancel the positive constant `rho`.
3. Apply `integral_mul_dq_on` componentwise. The support room hypothesis is
   exactly what turns the local set integrals into the global L2 summation by
   parts theorem without extending the PDE outside its domain.
4. Expand `diffQuot (B.a * weakGrad)` with `diffQuot_coeff_apply`, distribute
   the two terms in the differentiated standard test, and obtain the principal
   term plus the three cross terms.
5. Pass the exact four-term identity to `master_raw_nonsmooth`; `B.c = 0` and
   the homogeneous right side remove the zeroth-order and forcing terms.

## Current status

The public `subst_expand_on` now connects an unexpanded local standard-test
identity componentwise to `integral_mul_dq_on`, normalizes coefficient indices
by symmetry, divides by the positive coefficient scale, and produces the exact
principal-plus-three-cross-term identity. Its scalar parameter records the
local right-hand side, so both homogeneous and scalar-source weak equations can
reuse the same coefficient/global-witness algebra. The public
`hom_master_nonsmooth` consumes `DeGiorgi.exists_global_wit`, returns the global
representative and witness together with value and weak-gradient agreement on
the coefficient room, obtains the zero local identity from `homSol_substOn`,
and feeds the shared expansion to `master_raw_nonsmooth`.

Both direct dependencies are imported explicitly; the existing
`HomogeneousWeakSolution` import is retained. The refactor passed focused
verification without warnings, and its explicit named module refresh passed so
the source master could consume the new export. The resulting `SourceMaster`
module also passed its later explicit named refresh for a real downstream
consumer.

The canonical raw coercivity producer has been extracted in
`SubstitutionNonSmooth.lean`; the existing after-Young theorem reuses it rather
than retaining a duplicate proof.

## Progress

`hom_master_nonsmooth` remains behaviorally unchanged and focused-verified.
The shared source-capable expansion machinery is 100% complete at this focused
producer boundary. This is one producer in the compact-free
witness-native H2 chain; the larger P1c assembly remains substantially broader
and is not estimated from this local file alone.
