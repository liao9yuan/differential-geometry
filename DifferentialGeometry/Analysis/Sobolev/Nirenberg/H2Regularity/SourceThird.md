# Third-order scalar-source interior regularity

## Mathematical route

`srcSol_memW3_on` is the first fixed-order source recursion step.  For each
chosen first weak partial of `u`, `srcDiff_weak_eq` supplies an actual scalar
weak equation on the outer set.  Its source is

`chosenWeakPartial' 2 l f Omega + rho * homDiffSource B u Omega l`.

The first summand is square-integrable because `f ∈ W^{1,2}`; the second is
square-integrable by `homDiffSource_memLp` and `u ∈ W^{2,2}`.  The existing
compact-free interior theorem `srcSol_memW2_on` therefore gives two weak
derivatives of each chosen first derivative on the inner precompact set.  The
chosen derivative on the outer and inner domains is then identified almost
everywhere by `chosenWeakPartial'_mono_set_ae`, yielding `u ∈ W^{3,2}` on
the inner set.

## Reuse and scope

- Reuses the DifferentialGeometry-native differentiated equation and interior
  scalar-source `W^{2,2}` producer.
- Adds no assumptions, wrapper predicates, or replacement weak-solution API.
- This is a fixed-order producer.  It does not claim the all-order induction.

## Verification

Focused verification passed without warnings.  The explicitly named module
refresh also passed, so downstream imports see the current
`srcSol_memW3_on` declaration.
