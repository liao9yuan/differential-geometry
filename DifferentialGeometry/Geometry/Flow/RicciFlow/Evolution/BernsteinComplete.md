# BernsteinComplete

## Current state

`BernsteinTower` is now usable without `[CompactSpace M]`; compactness was
moved to the old closed-manifold consumers `estimate` and `estimate_div`.
That structural repair is focused-check green.

`BernsteinTower.estimate_complete` states the intended complete-noncompact
consumer with one fixed complete anchor metric, slabwise metric equivalence,
and a uniform Ricci lower bound.  It has one honest `sorry`.

Its tangent-space norm is now elaborated under the active anchor
`RiemannianBundle`, matching the geometric meaning of the displayed metric
equivalence and the HCG caller.  The prior exported statement had accidentally
used the model-fibre norm.  This statement repair is focused- and
targeted-green; it does not fill the analytic `sorry`.

## Exact frontier

The missing proof is a complete-noncompact scalar affine maximum principle for
the Bernstein barrier, obtained by compactly supported spatial cutoffs or an
exhaustion and then passage to the limit.  The current repository only has the
closed-manifold theorem `scalar_subsolution_affine_bound`; no complete-
noncompact parabolic maximum-principle theorem or cutoff package with the
required evolving-metric Laplacian control exists.

The remaining work is genuine analytic infrastructure, not a coercion or
typeclass repair.  It should be proved below `estimate_complete` and then used
inside the existing truncated-tower induction.  It must not be replaced by an
injectivity-radius assumption, a compactness assumption, or a new HCG input.

## Accounting

- `estimate_complete`: theorem-level 0% while its proof is `sorry`.
- Dedicated complete-Bernstein machinery: about 10%; the noncompact maximum
  principle is the dominant missing part.
- Unconditional `compactnessSol`: theorem-level 0%.
- Whole HCG support machinery: about 60%.
