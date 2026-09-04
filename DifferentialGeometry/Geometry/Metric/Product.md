# Product metric

## Mathematical route

The product metric is the sum of the two metric sections pulled back along
`Prod.fst` and `Prod.snd`. Smoothness is inherited directly from
`localPull_smooth` and combined with `ContMDiff.add_section`; no pullback proof is
duplicated here.

Positive definiteness is checked by splitting on the first component of a
nonzero product tangent vector. If it is zero, the second component is nonzero
and supplies strict positivity. Otherwise the first factor is strictly positive
and the second factor is nonnegative. Finite dimensionality then turns this
pointwise positive-definite form into the required bounded unit ball via
`Geometry.posDef_isVonNBounded` on `E × F`.

## Reuse and scope

- `prodMetric` is the canonical smooth Riemannian product metric.
- `prodMetric_inner` exposes its expected pointwise sum formula.
- The factor `SigmaCompactSpace` and `T2Space` assumptions are retained because
  the current global smooth pullback-section criterion uses them. The intended
  Busemann product factors already carry these instances, so this does not raise
  the splitting endpoint assumptions.
- No new predicate, instance, or alternative metric hierarchy is introduced.

## Verification status

The first focused checks reached only local proof-shape issues: after
`mfderiv_fst` and `mfderiv_snd` rewrote the derivatives, the deliberately narrow
`simp only` sets did not reduce the resulting continuous-linear projections to
the pair components, and the first repair still left the nested bilinear zero
applications opaque. Explicit `change` steps now expose the intended component
form. A later retry showed that directly rewriting the resulting zero term still
missed because of hidden dependent-fiber elaboration, despite identical printed
types. The proof now first establishes the zero equality on the original
`v.1`/`v.2` expression using `(g.inner x).map_zero` and
`ContinuousLinearMap.zero_apply`, then rewrites that exact expression. The
associated unused simp and section-variable warnings were removed. The source is
now warning-free under focused verification. The downstream-driven explicit
named refresh also passed, so `prodMetric` and `prodMetric_inner` are fresh for
the Busemann product consumer. No mathematical or API blocker remains in this
module.
