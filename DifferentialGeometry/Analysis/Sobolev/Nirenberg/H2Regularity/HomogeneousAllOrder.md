# HomogeneousAllOrder

## Mathematical route

`homSol_memWkp_on` is the homogeneous specialization of the checked
scalar-source producer `srcSol_memWkp_on`.

1. `hsol.to_homogeneous hOmega` gives the actual equality-form weak equation
   against every `H₀¹(Omega)` test and its native `W^{1,2}` membership.
2. A native witness is selected from that membership.
3. `MemWkp_zero_fun` supplies the zero scalar source in `W^{m,2}(Omega)` for
   every `m`.
4. The homogeneous equality is simplified to the scalar-source equation with
   right side `integral (0 * v)`, and `srcSol_memWkp_on` supplies
   `u ∈ W^{m+2,2}(V)`.

This specialization does not duplicate the all-order induction, require
compact closure of `Omega`, add a wrapper predicate, or strengthen the
coefficient assumptions.

## Reuse

Only `DifferentialGeometry`-native declarations are used:
`IsSolution.to_homogeneous`, `MemWkp_zero_fun`, and
`srcSol_memWkp_on`.  No reference-tree import or proof body is used.

## Verification

The first focused pass stopped before theorem elaboration because the canonical
`NirenbergEuclidean` namespace containing `SmoothEllipticBilinearForm` was not
opened.  The existing import already provides the type; the source now opens
that namespace without import churn or statement changes.

The corrected file passed a warning-free focused check, and its explicit named
module refresh also passed.  Downstream modules can therefore consume
`homSol_memWkp_on` without a stale artifact.  The proof contains no `sorry`,
`admit`, or new axiom.

The only expected local elaboration-sensitive points are inference of the zero
source function in the call to `srcSol_memWkp_on` and simplification of its
set-integral right side to the homogeneous equality.  Neither is a mathematical
or API blocker.
