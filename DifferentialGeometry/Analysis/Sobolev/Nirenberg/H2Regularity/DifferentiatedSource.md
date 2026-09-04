# DifferentiatedSource

## Target

Package the right-hand side obtained by differentiating a homogeneous
divergence-form equation as canonical data rather than as an extra assumption.
For

`F_l^i = sum_j (partial_l B_ij) (partial_j u)`,

the scalar source is defined componentwise as

`sum_i,j ((partial_i partial_l B_ij) (partial_j u)
  + (partial_l B_ij) (partial_i partial_j u))`.

The second derivatives of `u` are the canonical nested `chosenWeakPartial'`
functions on the same open set.

## Route

- `homDiffField` and `homDiffSource` are direct definitions using the global
  smooth coefficient field and the canonical weak partials.
- Smooth coefficients and their first two derivatives are bounded on
  `closure Omega`; multiplying those bounds by the `MemWkp 2 2` first and
  second weak partials gives the componentwise `L2` facts.
- Finite sums and `MemLp.of_eval_piLp` give `homDiffField_memLp` and
  `homDiffSource_memLp`.
- `HasWeakPartialDeriv.mul_smooth` supplies the product rule for each `(i,j)`
  term.  A private finite-sum assembly lemma gives the weak derivative of each
  vector component, and `hasWeakDiv_of_parts` proves `homDiff_hasDiv`.
- No new predicate, extra analytic assumption, or theorem-shaped wrapper is
  introduced.

## Verification

Focused verification and the explicit named export refresh both passed with no
reported warnings.  No broad build was run.

## Failed routes

No mathematical route failed.  Initial checks exposed two local elaboration
issues: the two terms of several double sums needed explicit parentheses to
remain inside both `Fin` binders, and the two `LocallyIntegrable` results passed
to `mul_smooth` needed enclosing parentheses.  Explicitly fixing the domain and
direction parameters of the finite-sum helper completed the same route.

The implementation deliberately avoided deriving the scalar source by
uniqueness of chosen weak derivatives, since the direct product rule followed
by `hasWeakDiv_of_parts` exposes the exact canonical formula with fewer
interfaces.

## Progress estimate

- `homDiffField`, `homDiffSource`, and their three requested facts: 100% as
  checked declarations.
- The differentiated-source data brick: 100%.
- The scalar-source local `W2` estimate remains unstated/unproved, 0%; this file
  supplies its canonical `L2` source and weak-divergence inputs.
- The all-order `MemWkp` bootstrap and P1c smooth-representative theorem remain
  unstated/unproved, 0%; their dedicated local elliptic machinery remains
  roughly 70% complete.
- The final P1 splitting theorem remains unstated/unproved, 0%.
