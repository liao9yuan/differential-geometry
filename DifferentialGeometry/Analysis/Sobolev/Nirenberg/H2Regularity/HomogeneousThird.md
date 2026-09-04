# Homogeneous local W3 regularity

## Result

`homSol_memW3` is the first fixed-order bootstrap endpoint above the checked
compact-free local `W^{2,2}` theorem.  On a relatively compact outer Euclidean
domain, a homogeneous divergence-form solution already in `W^{2,2}` belongs
to `W^{3,2}` on the inner cutoff domain.

The statement keeps the coefficient identity on all of the outer domain.  It
otherwise reuses the scalar-source `W^{2,2}` endpoint's cutoff, room, inner-set,
and cutoff-derivative assumptions verbatim.  It adds no solution predicate,
final-identity hypothesis, derivative bound for the coefficients, or other
consumer-side assumption.

## Proof route

Unfolding the successor clause for `MemWkp 3 2` reduces the result to local
`W^{2,2}` regularity of every canonical first weak partial.  For a direction
`l`, the differentiated weak-equation producer identifies the outer-domain
canonical partial as a scalar-source weak solution whose source is
`rho * homDiffSource B u Omega l`.  The source is square-integrable by
`homDiffSource_memLp`, so `srcSol_memW2` applies directly.

The scalar-source endpoint produces `W^{2,2}` for the canonical derivative
chosen on `Omega`.  `chosenWeakPartial'_mono_set_ae` identifies that function
almost everywhere on `V` with the canonical derivative chosen directly on
`V`; `MemWkp_congr_ae` transfers the result to the exact function required by
the successor clause.  The elementary inclusion `closure V ⊆ tsupport eta`
is proved by a file-private helper because the analogous helper in `Source`
is intentionally private to that module.

## Reuse and boundary

The implementation is entirely `DifferentialGeometry`-native.  It reuses the
checked scalar-source endpoint and the differentiated-source machinery; no
reference-tree theorem or proof body is imported or copied.  This closes only
the fixed `W^{2,2} -> W^{3,2}` step.  A generic source-differentiation recursion
and nested-domain induction are still required for all Sobolev orders.

## Verification

The first focused check exposed only a Unicode lambda-token parser mismatch and
a missing open for the coefficient namespace.  After those two mechanical
repairs, focused verification passed without warnings.  The explicit named
module refresh required by the next bootstrap consumer and the common axiom
audit also passed without warnings.

## Project position

- `homSol_memW3`: statement and proof warning-free verified (100% at this
  fixed-order endpoint).
- Dedicated fixed-order `W^3` assembly: 100% at this module boundary, with a
  fresh exported artifact available to downstream modules.
- The all-order local elliptic bootstrap, supplied-line splitting endpoint,
  and soul endpoint remain separate formal endpoints at 0%.
