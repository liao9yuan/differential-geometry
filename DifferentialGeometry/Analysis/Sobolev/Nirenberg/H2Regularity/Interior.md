# Interior scalar-source W2 wrapper

## Result

`srcSol_memW2_on` packages the canonical precompact-interior form of scalar-source
`W^{2,2}` regularity.  Its public hypotheses are only the open equation domain,
an open inner set with compact closure contained in that domain, the actual
scalar-source weak equation with an `L²` source, and the global smooth coefficient
realization already required by `srcSol_memW2`.

## Native route

The proof uses `exists_smooth_cutoff_with_neighborhood` with `closure V` as the
compact core, so the resulting cutoff equals one on a neighborhood of the whole
inner closure.  Because the cutoff has compact support inside `Omega`, its
topological support has a second positive closed-thickening still contained in
`Omega`; this supplies the coefficient room required by `srcSol_memW2`.  Smoothness
and compact support of the cutoff also bound its first derivative globally.

No cutoff, radius, derivative bound, solution predicate, or expanded identity is
exposed as an additional theorem hypothesis.

## Verification

Focused verification passed without warnings.  The explicit named module refresh
also passed once nested-domain induction became a real downstream consumer.

## Project position

- `srcSol_memW2_on`: formally stated, proved, and focused-verified.
- Dedicated nested-domain scalar-source `W²,²` machinery: complete at this
  wrapper boundary, with a fresh exported artifact available downstream.
- The all-order local elliptic bootstrap and P1c splitting theorem remain separate
  endpoints and are not advanced merely by this wrapper.
