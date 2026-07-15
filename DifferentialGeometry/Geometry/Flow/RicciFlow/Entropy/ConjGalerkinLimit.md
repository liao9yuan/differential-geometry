# Scalar conjugate-heat Galerkin compactness

## Role

`ConjGalerkinLimit.lean` is the compactness producer between the uniform finite
Galerkin energy theorem and the later identification of the limiting
coefficients with a spectral mild/strong solution.

The output predicate `IsConjGalSubseq` keeps the actual finite-dimensional ODE,
initial coefficients, off-truncation support, and all-order energy bounds.  It
also records one strictly monotone subsequence, modewise uniform convergence on
the common time interval, continuity of every limiting mode, the exact initial
coefficients, and inherited all-order weighted mass bounds.  This is not a
frontier wrapper: `scalar_gal_subseq` constructs every field from
`scalar_gal_bound`, the genuine operator bounds, and the generic compactness
producers.

## Proof route

The truncations are the rank-generic `eigenFinset` exhaustion.  Order-zero
energy bounds each scalar coefficient.  Order-two energy bounds the finite
`H²` vector, while `lapDiffA20_short` and `conjA1_short` bound the perturbation
operator.  The finite ODE therefore gives a support-independent, modewise
right-derivative bound.  `right_lipschitz` converts it to equi-Lipschitz control,
and `galerkin_subseq` extracts one subsequence uniformly in every countable
mode.  `fatou_sq_mass` passes each all-order energy bound to the limit.

No HCG compactness module, Aubin–Lions theorem, intrinsic Rellich `sorry`, chart
selector, or additional consumer assumption is used.

## Verification and frontier

The source for `scalar_gal_subseq` and its exact output predicate is written
without `sorry`.  Its upstream `scalar_gal_bound` focused verification passes;
this file still awaits its own check after the upstream module refresh, so
`scalar_gal_subseq` remains **0% verified**.  Its dedicated compactness
machinery is approximately **98% assembled**; remaining risk is local
elaboration, cumulative heartbeat, and normal-form repair in this assembly
theorem.

The next theorem, tentatively `scalar_gal_limit`, remains **0%**.  It must pass
the finite ODE integral identity to the limit and construct the spectral
mild/strong solution.  The classical moving conjugate-heat theorem and both
Perelman/Hamilton noncollapsing endpoints remain **0%**; this file advances only
their analytic machinery.

## Next spectral limit producer

The post-subsequence fixed-time producer is now source-written as `galLimHs`
and `galLim_tendsto`.  It packages `ulim t` as an `H^m` element using
`lim_mass`, constructs the difference at order `m+1`, and uses the public
`tendsto_of_coeff` at the strict downshift `m < m+1`.  Modewise convergence
comes from `conv`, the high-order norm bounds come from `energy` and
`lim_mass`, and eventual membership comes from the strictly monotone spectral
exhaustion.  No new convergence predicate or consumer assumption is used.

After verification, `scalar_gal_limit` can pass the finite right-derivative ODE to an
interval-integral identity by dominated convergence and package the result in
the existing `timeL2` / `timeH1` interfaces.  The genuine later frontier is the
bridge from the all-order spectral strong limit to joint spacetime smoothness
and `IsHeatPotOn`; the present intrinsic partition-of-unity all-order
completeness theorem is not yet that realization bridge.

Honest accounting before verification: `galLim_tendsto` is stated and
source-written but remains theorem-level **0% verified**, with approximately
**98%** of its dedicated machinery assembled;
`scalar_gal_limit` is unstated/unproved (0%) with roughly 35--45% dedicated
machinery.  `heatpot_of_maxreg`, the classical moving conjugate-heat theorem,
and both noncollapsing endpoints remain theorem-level 0%.
