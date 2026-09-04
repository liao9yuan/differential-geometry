# Homogeneous local W4 regularity

## Target

`homSol_memW4_on` is the fixed-order smoke test for the next Nirenberg
bootstrap step.  On a precompact open equation domain, a homogeneous
divergence-form solution already in `W^{3,2}` is asserted to belong to
`W^{4,2}` on every precompact open subset whose closure stays in the outer
domain.

## Mathematical route

The successor characterization of `MemWkp 4 2` reduces the endpoint to
`W^{3,2}` regularity of each canonical first weak partial.  For a direction
`l`, `homDiff_weak_eq` gives the actual scalar weak equation for the derivative
chosen on the outer domain.  Its source is

`rho * homDiffSource B u Omega l`.

`homDiff_memW1` puts the unscaled source in `W^{1,2}` from the input
`u in W^{3,2}`; the existing constant-scalar action preserves that regularity.
The fixed scalar-source endpoint `srcSol_memW3_on` then supplies `W^{3,2}` for
the outer-domain chosen derivative on the inner set.  Finally,
`chosenWeakPartial'_mono_set_ae` and `MemWkp_congr_ae` identify it with the
canonical derivative selected directly on the inner set.

No new weak-solution predicate, coefficient hypothesis, derivative bound, or
final-identity assumption is introduced.

## Verification

Focused verification passed without warnings.  The explicit named export
refresh required by the next all-order smoke test and the common axiom audit
also passed without warnings.

## Project position

- `homSol_memW4_on`: formally stated, proved, focused-verified, and refreshed;
  100% at this fixed-order endpoint.
- Dedicated fixed-order `W^4` assembly: 100% at this module boundary.
- The generic all-order local elliptic bootstrap, Cheeger--Gromoll splitting
  endpoint, and soul endpoint remain separate unstated/unproved endpoints at
  0%.
